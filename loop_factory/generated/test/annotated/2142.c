int main1(){
  int k, j9, p4, le, y1zw, c;
  k=51;
  j9=0;
  p4=12;
  le=4;
  y1zw=j9;
  c=j9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (p4 == 12 + j9);
  loop invariant (0 <= j9 && j9 <= k);
  loop invariant (y1zw == 0);
  loop invariant (k == 51);
  loop invariant c*c + le*le - c*le == 16;
  loop invariant c % 4 == 0;
  loop invariant le % 4 == 0;
  loop assigns c, p4, j9, le;
*/
while (j9 < k) {
      c = c - le + y1zw;
      p4 += 1;
      j9++;
      le = le + c;
  }
}