`include "vaddsub_if.vh"
`include "vector_if.vh"
`include "vector_types.vh"

`timescale 1 ns / 1 ns

module vaddsub_tb;

    parameter PERIOD = 10ns;
    logic CLK = 0, nRST;
    logic [15:0] exp;
    int casenum;
    string casename;
    logic done_testing = 0;


    vaddsub_if vaddsubif ();
    vaddsub DUT (.CLK(CLK), .nRST(nRST), .vaddsubif(vaddsubif));

    // Clock generation
    always #(PERIOD/2) CLK = ~CLK;

    
    task automatic test_case(
        input logic [15:0] a,
        input logic [15:0] b,
        input logic sub);
    begin

        @(negedge CLK);

        vaddsubif.enable = 1;
        vaddsubif.sub = sub;
        vaddsubif.port_a = a;
        vaddsubif.port_b = b;

        @(negedge CLK);

        vaddsubif.enable = 0;
    end
    endtask //automatic

    task automatic check_case(
        input string casename,
        input logic [15:0] expected);
    begin
        if (vaddsubif.out !== expected) begin
            $display("Failed Test for %s: A=%h B=%h Got=%h Exp=%h", casename, vaddsubif.port_a, vaddsubif.port_b, vaddsubif.out, expected);
        end
        else begin
            $display("Passed %s | A=%h B=%h Got=%h Exp=%h", casename, vaddsubif.port_a, vaddsubif.port_b, vaddsubif.out, expected);
        end
    end
    endtask //automatic
    

    // Special Case Values
    localparam logic [15:0] P_INF = 16'b0_11111_0000000000,
    N_INF   = 16'b1_11111_0000000000,
    NAN = 16'b0_11111_0100000000,
    P_ZERO = 16'b0_00000_0000000000,
    N_ZERO = 16'b1_00000_0000000000,
    ONE = 16'b0_01111_0000000000,
    TWO = 16'b0_10000_0000000000,
    MIN = 16'b0_00000_0000000001,
    MAX_FINITE= 16'b0_11110_1111111111;


initial begin
    
    nRST = '0;

    #(PERIOD);

    nRST = 1;

    test_case(ONE, ONE, 0);
    exp = 16'b0_10000_0000000000;
    #(PERIOD);
    check_case("1 + 1 = 2", exp);
    #(PERIOD);


    test_case(TWO, ONE, 1);
    exp = 16'b0_01111_0000000000; 
    #(PERIOD);
    check_case("2 - 1 = 1", exp);
    #(PERIOD);

    test_case(16'b1_10000_1000000000, 16'b0_10000_0000000000, 0);
    exp = 16'b1_01111_0000000000;
    #(PERIOD);
    check_case("(-3) + 2 = -1", exp);
    #(PERIOD);

    // ---------------- Zeroes ----------------
    test_case(P_ZERO, P_ZERO, 0);
    exp = P_ZERO;
    #(PERIOD);
    check_case("+0 + +0", exp);
    #(PERIOD);

    test_case(P_ZERO, N_ZERO, 0);
    exp = P_ZERO;
    #(PERIOD);
    check_case("+0 + -0", exp);
    #(PERIOD);

    test_case(N_ZERO, N_ZERO, 1);
    exp = P_ZERO;
    #(PERIOD);
    check_case("-0 - -0", exp);
    #(PERIOD);

    test_case(ONE, P_ZERO, 0);
    exp = ONE;
    #(PERIOD);
    check_case("+x + 0", exp);
    #(PERIOD);

    // ---------------- Infinities ----------------
    test_case(P_INF, ONE, 0);
    exp = P_INF;
    #(PERIOD);
    check_case("+Inf + finite", exp);
    #(PERIOD);

    test_case(N_INF, ONE, 1);
    exp = N_INF;
    #(PERIOD);
    check_case("-Inf - finite", exp);
    #(PERIOD);

    test_case(P_INF, P_INF, 0);
    exp = P_INF;
    #(PERIOD);
    check_case("+Inf + +Inf", exp);
    #(PERIOD);

    test_case(N_INF, N_INF, 0);
    exp = N_INF;
    #(PERIOD);
    check_case("-Inf + -Inf", exp);
    #(PERIOD);

    test_case(P_INF, N_INF, 0);
    exp = NAN;
    #(PERIOD);
    check_case("+Inf + -Inf = NaN", exp);
    #(PERIOD);

    test_case(P_INF, P_INF, 1);
    exp = NAN;
    #(PERIOD);
    check_case("+Inf - +Inf = NaN", exp);
    #(PERIOD);

    test_case(ONE, N_INF, 1);
    exp = P_INF;
    #(PERIOD);
    check_case("finite - (-Inf) = +Inf", exp);
    #(PERIOD);

    test_case(ONE, P_INF, 1);
    exp = N_INF;
    #(PERIOD);
    check_case("finite - (+Inf) = -Inf", exp);
    #(PERIOD);

    // ---------------- NaN ----------------
    test_case(NAN, ONE, 0);
    exp = NAN;
    #(PERIOD);
    check_case("NaN + 1 = NaN", exp);
    #(PERIOD);

    test_case(ONE, NAN, 1);
    exp = NAN;
    #(PERIOD);
    check_case("1 - NaN = NaN", exp);
    #(PERIOD);

    // ---------------- Subnormals ----------------
    test_case(MIN, ONE, 0);
    exp = ONE;
    #(PERIOD);
    check_case("subnormal + 1 ≈ 1", exp);
    #(PERIOD);

    test_case(MIN, MIN, 0);
    exp = P_ZERO; // changed to 0, cause of DAZ
    #(PERIOD);
    check_case("subnormal + subnormal", exp);
    #(PERIOD);

    test_case(MIN, MIN, 1);
    exp = P_ZERO;
    #(PERIOD);
    check_case("subnormal - subnormal = 0", exp);
    #(PERIOD);

    test_case(TWO, MIN, 0);
    exp = TWO; // Doesn't change as DAZ means we treat subnormals as zero
    #(PERIOD);
    check_case("large_x + subnormal ≈ large_x", exp);
    #(PERIOD);

    // ---------------- Overflow / Underflow ----------------
    test_case(MAX_FINITE, MAX_FINITE, 0);
    exp = P_INF;
    #(PERIOD);
    check_case("overflow: max + max = +Inf", exp);
    #(PERIOD);

    test_case(16'b1_11110_1111111111, 16'b1_11110_1111111111, 0);
    exp = N_INF;
    #(PERIOD);
    check_case("overflow: -max + -max = -Inf", exp);
    #(PERIOD);

    test_case(MIN, MIN, 1);
    exp = P_ZERO;
    #(PERIOD);
    check_case("underflow: tiny - tiny = 0", exp);
    #(PERIOD);

    // ---------------- Cancellation ----------------
    test_case(16'b0_10000_1000000000, 16'b1_10000_1000000000, 0);
    exp = P_ZERO;
    #(PERIOD);
    check_case("+x + (-x) = +0", exp);
    #(PERIOD);

    test_case(16'b0_10000_1000000000, 16'b0_10000_1000000000, 1);
    exp = P_ZERO;
    #(PERIOD);
    check_case("+x - (+x) = +0", exp);
    #(PERIOD);

    // ---------------- Sign checks ----------------
    test_case(16'b0_10000_0000000000, 16'b0_10000_0000000000, 0);
    exp = 16'b0_10001_0000000000;
    #(PERIOD);
    check_case("+a + +b = +", exp);
    #(PERIOD);

    test_case(16'b1_10000_0000000000, 16'b1_10000_0000000000, 0);
    exp = 16'b1_10001_0000000000;
    #(PERIOD);
    check_case("-a + -b = -", exp);
    #(PERIOD);

    test_case(16'b0_10000_0000000000, 16'b1_10000_0000000000, 1);
    exp = 16'b0_10001_0000000000;
    #(PERIOD);
    check_case("+a - (-b) = +", exp);
    #(PERIOD);

    test_case(16'b1_10000_0000000000, 16'b0_10000_0000000000, 1);
    exp = 16'b1_10001_0000000000;
    #(PERIOD);
    check_case("-a - (+b) = -", exp);
    #(PERIOD);

    done_testing = 1;
end    
// Changed this a bit from previous version but have also commented it out for now
// as I don't use it for my approach to testing the vaddsub module.
    /*
    casenum = '0;
    casename = "nRST";

    nRST = '0;

    #(PERIOD);

    nRST = 1;

    casenum = 1;
    casename = "Add Case 1: ";

    vaddsubif.enable = 1;
    vaddsubif.sub = 0;
    vaddsubif.port_a = 16'b0_01111_0000000001;
    vaddsubif.port_b = 16'b0_01111_0000000011;

    #(PERIOD);

    casenum = 2;
    casename = "Add Case 2";

    vaddsubif.port_a = 16'b0_10000_0000000001;
    vaddsubif.port_b = 16'b0_01111_0000000011;

    #(PERIOD);

    casenum = 3;
    casename = "Overflow Case";

    vaddsubif.port_a = 16'b0_10000_1000000000;
    vaddsubif.port_b = 16'b0_01111_1100000000;

    #(PERIOD);

    casenum = 4;
    casename = "Subtract Case 1 w Adder";

    vaddsubif.port_a = 16'b0_10000_1000000000;
    vaddsubif.port_b = 16'b1_01111_1100000000;

    #(PERIOD);

    casenum = 5;
    casename = "Subtract Case 2 w Adder";

    vaddsubif.port_a = 16'b0_10000_1000000000;
    vaddsubif.port_b = 16'b1_10001_0010000000;

    #(PERIOD);

    casenum = 6;
    casename = "Add Case 3 Two Negatives";

    vaddsubif.port_a = 16'b1_10001_0010000000;
    vaddsubif.port_b = 16'b1_10000_1000000000;

    #(PERIOD);

    casenum = 7;
    casename = "Subtract Case 1 Positive - Negative";

    vaddsubif.sub = 1;
    vaddsubif.port_a = 16'b0_10001_0010000000;
    vaddsubif.port_b = 16'b0_10000_1000000000;

    #(PERIOD);

    casenum = 7;
    casename = "Subtract Case 2 Postive - Negative";

    vaddsubif.sub = 1;
    vaddsubif.port_a = 16'b0_10001_0010000000;
    vaddsubif.port_b = 16'b1_10000_1000000000;
    
    #(PERIOD);

    casenum = 8;
    casename = "Subtract Case 3 Negative - Negative";

    vaddsubif.sub = 1;
    vaddsubif.port_a = 16'b1_10001_0010000000;
    vaddsubif.port_b = 16'b1_10000_1000000000;
    
    #(PERIOD);
    */

    // ---------------- RANDOM TESTING ----------------
integer fd;                 // file descriptor
string header;              // to skip first line
string a_str, b_str, exp_str;
int sub;
logic [15:0] a, b, expected;

initial begin
    wait(done_testing);
    #10ns;

    fd = $fopen("test_data/random_cases.csv", "r");
    if (fd == 0) begin
        $fatal("ERROR: Could not open random_cases.csv");
    end
    else begin
        $display("Opened random_cases.csv for reading.");
    end

    // Skip header row ("a,b,sub,expected")
    void'($fgets(header, fd));

    // Read until end of file
    // Read format: hex_a,hex_b,sub,hex_expected
    while (!$feof(fd)) begin
        int ret;
        ret = $fscanf(fd, "%s,%s,%d,%4s\n", a_str, b_str, sub, exp_str);
        if (ret != 4) continue; // Skip malformed lines

        // Convert string → 16-bit value
        // Issues with questa, have to use void'$sscanf
        void'($sscanf(a_str, "%h", a));
        void'($sscanf(b_str, "%h", b));
        void'($sscanf(exp_str, "%h", expected));


        // Apply to DUT
        @(negedge CLK);
        vaddsubif.enable = 1;
        vaddsubif.sub    = sub;
        vaddsubif.port_a = a;
        vaddsubif.port_b = b;

        @(negedge CLK);
        vaddsubif.enable = 0;
        #(PERIOD);

        // Compare result
        if (vaddsubif.out !== expected)
            $display("FAIL | A=%h  B=%h  SUB=%0d → Got=%h  Exp=%h", a, b, sub, vaddsubif.out, expected);
        else
            $display("PASS | A=%h  B=%h  SUB=%0d → %h", a, b, sub, vaddsubif.out);
    end

    $fclose(fd);
    $finish;;
end

    
endmodule