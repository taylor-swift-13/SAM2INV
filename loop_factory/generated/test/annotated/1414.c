int main1(int j){
  int ep, p6, d7cc, n0e;
  ep=j+23;
  p6=ep;
  d7cc=-2;
  n0e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ep == j + 23;
  loop invariant n0e == 0 || n0e == -2;
  loop invariant d7cc == -2 || d7cc == ep - 2;
  loop invariant p6 == 1 || p6 == ep;
  loop invariant ((n0e == 0 && d7cc == -2 && p6 == ep) ||
                    (n0e == -2 && d7cc == ep - 2 && p6 == 1));
  loop invariant ep == \at(j, Pre) + 23 && (p6 == 1 || p6 == ep);
  loop invariant d7cc >= -2;
  loop invariant ((p6 == ep && d7cc == -2 && n0e == 0) ||
                    (p6 == 1 && d7cc == -2 + ep && n0e == -2));
  loop assigns n0e, d7cc, p6;
*/
while (p6>=2) {
      n0e = n0e + d7cc;
      d7cc += p6;
      p6 = 1;
  }
}