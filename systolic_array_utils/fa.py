n = int(input("stage #: "))
x = int(input("fa start #: "))
y = int(input("fa end #: "))

if (n == 1): 
    a1 = int(input("first a index: "))
    b1 = int(input("first b index: "))
    a2 = int(input("second a index: "))
    b2 = int(input("second b index: "))
    a3 = int(input("third a index: "))
    b3 = int(input("third b index: "))
elif (n == 5): 
    b1 = int(input("first cin start: "))
    b2 = int(input("sin start: ")) 
    a3 = int(input("third a index: "))
    b3 = int(input("third b index: "))
else: 
    b1 = int(input("first cin start: "))
    b2 = int(input("sin start: ")) 
    b3 = int(input('second cin start: '))
s = int(input("s: "))
c = int(input("c: "))

for i in range (x, y + 1): 
    if (n == 1): 
        print(f"fa fa{n-1}{i} (.a(A[{a1}] && B[{b1}]), .b(A[{a2}] && B[{b2}]), .cin(A[{a3}] && B[{b3}]), .s(s[{s}]), .cout(c[{c}]));")
    elif (n == 5): 
        print(f"fa fa{n-1}{i} (.a(c[{b1}]), .b(s[{b2}]), .cin(A[{a3}] && B[{b3}]), .s(s[{s}]), .cout(c[{c}]));")
    elif (n == 6): 
        print(f"fa fa{n-1}{i} (.a(c[{b1}]), .b(s[{b2}]), .cin(c[{b3}]), .s(S[{s}]), .cout(c[{c}]));")
    else: 
        # print(f"fa fa{n-1}{i} (.a(c[{b1}]), .b(s[{b2}]), .cin(c[{b3}]), .s(s[{s}]), .cout(c[{c}]));")
        # print(f"fa fa{n-1}{i} (.a(s[{b1}]), .b(c[{b2}]), .cin(s[{b3}]), .s(s[{s}]), .cout(c[{c}]));")
        print(f"fa fa{n-1}{i} (.a(c[{b1}]), .b(s[{b2}]), .cin(s[{b3}]), .s(s[{s}]), .cout(c[{c}]));")
    b1 += 1 
    b2 += 1
    b3 += 1 
    s += 1
    c += 1