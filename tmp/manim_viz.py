from manim import * 


class SystolicArray(Scene):
    def construct(self):
        # Activation Matrix (Positioned lower-left)
        H = 6  # Number of rows
        W = 6  # Number of columns

        matrix_values = [[(i * W + j + 1) for j in range(W)] for i in range(H)]
        activation_matrix = Matrix(matrix_values)
        activation_matrix.scale(0.5)
        activation_matrix.shift(DOWN * 2.5 + LEFT * 4.5)  # Lower-left positioning
        
        # Semi-transparent red background overlay for activation matrix
        activation_overlay = SurroundingRectangle(
            activation_matrix, color=RED, fill_opacity=0.3, fill_color=RED
        )

        # Animate activation matrix with overlay
        self.play(Write(activation_matrix))
        self.play(FadeIn(activation_overlay))

        # Weight Matrix (Positioned lower-left, but slightly to the right)
        R = 4  # Number of rows
        S = 4  # Number of columns

        matrix_values2 = [[(i * S + j + 1) for j in range(S)] for i in range(R)]
        weight_matrix = Matrix(matrix_values2)
        weight_matrix.scale(0.5)
        weight_matrix.shift(DOWN * 2.5 + LEFT * 1.2)  # Slightly to the right

        # Semi-transparent green background overlay for weight matrix
        weight_overlay = SurroundingRectangle(
            weight_matrix, color=GREEN, fill_opacity=0.3, fill_color=GREEN
        )

        # Animate weight matrix with overlay
        self.play(Write(weight_matrix))
        self.play(FadeIn(weight_overlay))


        grid_size = 4
        square_side = 1       # Side length of each square
        spacing = 1.2         # Adjusted spacing for better placement
        square_color = BLUE   # Square color
        
        # Create a VGroup to hold all squares
        squares = VGroup()
        
        # Create grid of squares with centered text labels
        X_OFFSET = 2
        Y_OFFSET = 3

        squares = VGroup()
        buffer_rectangles = VGroup()
        buffer_texts = VGroup()
        arrows = VGroup()

        grid_size = 4
        square_side = 1  # Side length of each square
        spacing = 1.2  # Adjusted spacing for better placement
        square_color = BLUE  # Square color

        grid_size = 4
        square_side = 1  # Side length of each square
        spacing = 1.2  # Adjusted spacing for better placement
        square_color = BLUE  # Square color

        # Create a VGroup to hold all squares
        squares = VGroup()
        buffer_rectangles = VGroup()
        buffer_texts = [[None for _ in range(3)] for _ in range(grid_size)]  # Track text objects for updates

        X_OFFSET = 5
        Y_OFFSET = 3
        buffer_width = 3  # Adjust to elongate left
        buffer_height = square_side * 0.8  # Matches systolic array row height

        # Define values for buffers (left-to-right)
        buffer_values = [
            ['A00', 'A10', 'A20', 'A30', 'A02', 'A12', 'A22', 'A32', 'A20', 'A30', 'A40', 'A50', 'A22', 'A32', 'A42', 'A52', '0', '0', '0'],
            ['0',  'A01', 'A11', 'A21', 'A31', 'A03', 'A13', 'A23', 'A33', 'A21', 'A31', 'A41', 'A51', 'A23', 'A33', 'A43', 'A53', '0', '0'],
            ['0',  '0', 'A02', 'A12', 'A22', 'A32', 'A04', 'A14', 'A24', 'A34', 'A22', 'A32', 'A42', 'A52', 'A24', 'A34', 'A44', 'A54', '0'],
            ['0', '0', '0', 'A03', 'A13', 'A23', 'A33', 'A05', 'A15', 'A25', 'A35', 'A23', 'A33', 'A43', 'A53', 'A25', 'A35', 'A45', 'A55']
        ]

        num_display_values = 3  # Start with the first 3 values in each buffer
        spacing_values = np.linspace(-4.3, -3.0, num_display_values)  # Left to right positions

        # Function to get (X, Y) position for each buffer value
        def get_buffer_position(buffer_index, value_index):
            """Returns (X, Y) position for each value in a buffer."""
            x_pos = X_OFFSET + spacing_values[value_index] + 1
            y_pos = Y_OFFSET - buffer_index * spacing
            return np.array([x_pos, y_pos, 0])

        # Create buffers and initialize the first 3 values in each row
        for i in range(grid_size):
            for j in range(grid_size):
                square = Square(side_length=square_side, color=square_color)
                square.set_fill(square_color, opacity=0.5)
                square.move_to(np.array([X_OFFSET + j * spacing, Y_OFFSET - i * spacing, 0]))

                label = Text(f"({i},{j})", font_size=16)
                label.move_to(square.get_center())
                square.add(label)
                squares.add(square)

            # Create a buffer rectangle to the left of each row
            buffer = Rectangle(
                width=buffer_width, height=buffer_height, color=ORANGE, fill_opacity=0.6
            )
            buffer.move_to(np.array([X_OFFSET - 3.5 - spacing, Y_OFFSET - i * spacing, 0]))
            buffer_rectangles.add(buffer)

            # Add initial values to the buffer
            for j in range(num_display_values):
                value = buffer_values[i][j]  # Get the initial value
                text = Text(value, font_size=16)
                text.move_to(get_buffer_position(i, j))  # Use spacing array for position
                buffer_texts[i][j] = text  # Store reference
                self.add(text)

        # Animate systolic array and buffers
        self.play(Create(squares))
        self.play(FadeIn(buffer_rectangles))
        self.wait(1)

        # Incrementally update buffers every 2 seconds
        for step in range(num_display_values, len(buffer_values[0])):  # Start from index 3 to end
            animations = []
            for i in range(grid_size):
                # Remove leftmost value
                self.remove(buffer_texts[i][0])

                # Shift all existing values left
                for j in range(num_display_values - 1):
                    buffer_texts[i][j] = buffer_texts[i][j + 1]
                    animations.append(buffer_texts[i][j].animate.move_to(get_buffer_position(i, j)))

                # Insert new value at rightmost position
                new_value = buffer_values[i][step]
                new_text = Text(new_value, font_size=16)
                new_text.move_to(get_buffer_position(i, num_display_values - 1))  # Rightmost position
                buffer_texts[i][num_display_values - 1] = new_text
                animations.append(Write(new_text))

            # Play animations together
            self.play(*animations)
            self.wait(2)  # Wait 2 seconds before the next update

        self.wait(3)