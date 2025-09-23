from math import ceil
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import ListedColormap
from matplotlib.patches import Patch

NUM_BANKS = 32

class AddressBlock:
    @staticmethod
    def _row_lane(abs_row: int, cols: int):
        low5 = abs_row & (NUM_BANKS - 1)
        banks = [(lane ^ low5) & (NUM_BANKS - 1) for lane in range(NUM_BANKS)]
        slots = [abs_row] * NUM_BANKS
        valid = [(lane < cols) for lane in range(NUM_BANKS)]
        return banks, slots, valid

    @staticmethod
    def _col_lane(base_row: int, col_id: int, rows: int):
        banks = []
        slots = []
        valid = []
        for lane in range(NUM_BANKS):
            abs_row = base_row + lane
            bank = (col_id ^ (abs_row & (NUM_BANKS - 1))) & (NUM_BANKS - 1)
            banks.append(bank)
            slots.append(abs_row)
            valid.append(lane < rows)
        return banks, slots, valid

    @staticmethod
    def gen_masks_row(base_row: int, row_id: int, cols: int):
        abs_row = base_row + row_id
        lane_bank, lane_slot, lane_valid = AddressBlock._row_lane(abs_row, cols)

        shift_mask_lane2bank = [(lane_bank[i] if lane_valid[i] else None) for i in range(NUM_BANKS)]
        slot_mask = [None] * NUM_BANKS
        for i in range(NUM_BANKS):
            if lane_valid[i]:
                b = lane_bank[i]
                slot_mask[b] = lane_slot[i] 

        return shift_mask_lane2bank, slot_mask, lane_bank, lane_slot, lane_valid

    @staticmethod
    def gen_masks_col(base_row: int, col_id: int, rows: int):
        lane_bank, lane_slot, lane_valid = AddressBlock._col_lane(base_row, col_id, rows)

        shift_mask_lane2bank = [(lane_bank[i] if lane_valid[i] else None) for i in range(NUM_BANKS)]
        slot_mask = [None] * NUM_BANKS
        for i in range(NUM_BANKS):
            if lane_valid[i]:
                b = lane_bank[i]
                slot_mask[b] = lane_slot[i]  

        return shift_mask_lane2bank, slot_mask, lane_bank, lane_slot, lane_valid


def _parse_cell_triplet(cell: str):
    if not cell:
        return "", None, None
    parts = cell.split("_")
    if len(parts) < 3:
        return "", None, None
    try:
        r = int(parts[-2])
        c = int(parts[-1])
    except ValueError:
        return "", None, None
    tid = "_".join(parts[:-2])
    return tid, r, c

def save_png(sc0, path: str, annotate: bool=True, grid: bool=True):
    B, S = sc0.B, sc0.S

    tile_grid = [["" for _ in range(B)] for _ in range(S)]
    rc_grid = [[(None, None) for _ in range(B)] for _ in range(S)]
    tile_ids = set()

    for b in range(B):
        for s in range(S):
            tid, r, c = _parse_cell_triplet(sc0.banks[b][s])
            tile_grid[s][b] = tid
            rc_grid[s][b] = (r, c)
            if tid:
                tile_ids.add(tid)

    tile_ids = sorted(list(tile_ids))
    tid_to_idx = {tid: i+1 for i, tid in enumerate(tile_ids)}  

    idx_grid = np.zeros((S, B), dtype=int)
    for s in range(S):
        for b in range(B):
            tid = tile_grid[s][b]
            idx_grid[s, b] = tid_to_idx.get(tid, 0)

    base_colors = list(plt.cm.tab20.colors) + list(plt.cm.tab20b.colors) + list(plt.cm.tab20c.colors)
    if len(tile_ids) > len(base_colors):
        extra = len(tile_ids) - len(base_colors)
        hsv = [matplotlib.colors.hsv_to_rgb((h/max(1, extra), 0.5, 0.95)) for h in range(extra)]
        base_colors += hsv
    colors = ["white"] + base_colors[:len(tile_ids)]
    cmap = ListedColormap(colors)

    fig_w = max(20, B * 0.55) # 32 = B  -> banks
    fig_h = max(14, S * 0.35)  # 64 = S -> slots 
    fig, ax = plt.subplots(figsize=(fig_w, fig_h), dpi=350)
    im = ax.imshow(idx_grid, cmap=cmap, aspect="auto", interpolation="nearest", origin="upper")

    ax.set_xlabel("Bank (0..{})".format(B-1))
    ax.set_ylabel("Slot (0..{})".format(S-1))
    ax.set_xticks(np.arange(0, B, max(1, B//16)))
    ax.set_yticks(np.arange(0, S, max(1, S//16)))

    if grid:
        ax.set_xticks(np.arange(-0.5, B, 1), minor=True)
        ax.set_yticks(np.arange(-0.5, S, 1), minor=True)
        ax.grid(which="minor", linestyle="-", linewidth=0.2, alpha=0.4)

    if annotate:
        for s in range(S):
            for b in range(B):
                tid = tile_grid[s][b]
                if tid:
                    r, c = rc_grid[s][b]
                    # two-line text: tile_id on top, (r,c) below
                    ax.text(b, s-0.22, tid, ha='center', va='center', fontsize=5, fontweight='bold')
                    if r is not None and c is not None:
                        ax.text(b, s+0.22, f"({r},{c})", ha='center', va='center', fontsize=5)

    if tile_ids:
        patches = [Patch(facecolor=colors[tid_to_idx[tid]], edgecolor='black', label=tid) for tid in tile_ids]
        leg_cols = 1 if len(patches) < 12 else 2
        ax.legend(handles=patches, bbox_to_anchor=(1.02, 1), loc='upper left',
                  borderaxespad=0., ncol=leg_cols, title="Tile IDs")

    ax.set_title("Scratch0 Overview with Logical (row,col) per Cell")
    plt.tight_layout()
    plt.savefig(path, bbox_inches="tight")
    plt.close(fig)
    return path

class Scratchpad:
    def __init__(self, slots_per_bank: int):
        self.B = NUM_BANKS
        self.S = slots_per_bank

        self.banks = [["" for _ in range(self.S)] for _ in range(self.B)]
        self.tiles = {} 

    def clear(self):
        for b in range(self.B):
            for s in range(self.S):
                self.banks[b][s] = ""

    def write_tile(self, tile_id: str, rows: int, cols: int, base_row: int, strict: bool = True):
        assert 0 <= cols <= NUM_BANKS, "Tile width must be <= NUM_BANKS (tile externally if wider)."

        stored = 0
        dropped = 0
        trace: List[Dict[str, Any]] = []

        for r in range(rows):
            print('----')
            abs_row = base_row + r

            dram_vec: List[Optional[str]] = [None] * self.B

            # simulate DRAM read out 
            for i in range(self.B):
                flat = r * cols + i
                rr = flat // cols if cols > 0 else 0
                cc = flat %  cols if cols > 0 else 0
                if rr < rows and cc < cols:
                    dram_vec[i] = f"{tile_id}_{rr}_{cc}"

            shift_mask, slot_mask, _, _, _ = AddressBlock.gen_masks_row(base_row=base_row, row_id=r, cols=cols)

            switch_out = SwitchingNetwork.route(shift_mask, dram_vec)

            for bank, val in enumerate(switch_out):
                s = slot_mask[bank]
                if s is None: continue 

                if not (0 <= s < self.S):
                    raise ValueError(f"Out-of-range write: bank={bank}, slot={s}")
                    dropped += 1
                    continue

                self.banks[bank][s] = val
                stored += 1

        self.tiles[tile_id] = {"rows": rows, "cols": cols, "base_row": base_row}
        return {"stored": stored, "dropped": dropped}

    def read_tile(self, tile_id: str, base_row: int, row_id: int = 0, col_id: int = 0, row_based: bool = True):

        def _read(slot_mask): 
            bank_inputs = [0] * B
            for b in range(B):
                s = slot_mask[b]
                if s is not None:
                    bank_inputs[b] = self.banks[b][s]
            return bank_inputs

        assert tile_id in self.tiles
        rows = self.tiles[tile_id]["rows"]
        cols = self.tiles[tile_id]["cols"]
        B = self.B

        if row_based:
            assert 0 <= row_id < rows

            shift_lane2bank, slot_mask, _, _, _ = AddressBlock.gen_masks_row(base_row, row_id, cols)
            bank_inputs = _read(slot_mask)

            # In hardware, we can just do bank_inputs[shift_lane2bank[i]]
            bank_to_lane = [None] * B
            for lane, bank in enumerate(shift_lane2bank):
                if bank is not None:
                    bank_to_lane[bank] = lane
            lane_out = SwitchingNetwork.route(bank_to_lane, bank_inputs)

            golden = [(f"{tile_id}_{row_id}_{c}" if c < cols else 0) for c in range(NUM_BANKS)]
            mode = "row"

        else:
            assert 0 <= col_id < cols

            shift_lane2bank, slot_mask, _, _, _ = AddressBlock.gen_masks_col(base_row, col_id, rows)
            bank_inputs = _read(slot_mask)

            # In hardware, we can just do bank_inputs[shift_lane2bank[i]]
            bank_to_lane = [None] * B
            for lane, bank in enumerate(shift_lane2bank):
                if bank is not None:
                    bank_to_lane[bank] = lane
            lane_out = SwitchingNetwork.route(bank_to_lane, bank_inputs)

            golden = [ (f"{tile_id}_{r}_{col_id}" if r < rows else 0) for r in range(NUM_BANKS) ]
            mode = "col"

        mismatches = [(i, lane_out[i], golden[i]) for i in range(B) if lane_out[i] != golden[i]]

        return {
            "mode": mode,
            "slot_mask": slot_mask,
            "shift_mask_inv": shift_lane2bank,
            "bank_inputs": bank_inputs,
            "shift_mask": bank_to_lane,
            "lane_out": lane_out,
            "golden": golden,
            "pass": len(mismatches) == 0,
            "mismatches": mismatches
        }
