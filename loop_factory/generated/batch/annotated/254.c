int main1(int b,int m){
  int p, c, a;

  p=61;
  c=1;
  a=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c >= 1;
  loop invariant c <= p;
  loop invariant p == 61;
  loop invariant m == \at(m, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant c >= 1 && (c == 1 || c % 2 == 0) && c <= p;
  loop assigns c;
*/
while (c*2<=p) {
      c = c*2;
  }

}
