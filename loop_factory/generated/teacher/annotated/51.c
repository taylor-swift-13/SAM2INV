int main1(int m,int p){
  int w, e, c, v, k;

  w=59;
  e=0;
  c=-4;
  v=w;
  k=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == -4 + 3*e;
  loop invariant k == -6 + 2*e;
  loop invariant 0 <= e && e <= w;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant e >= 0;
  loop invariant e <= w;
  loop assigns c, k, e;
*/
while (e<w) {
      c = c+3;
      k = k+2;
      e = e+1;
  }

}
