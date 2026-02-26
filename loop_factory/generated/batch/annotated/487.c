int main1(int p,int q){
  int e, j, v, g;

  e=q;
  j=e;
  v=e;
  g=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == q;
  loop invariant j <= e;
  loop invariant v == e + (j - e) * (1 + 2*g);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant g == 6;
  loop invariant v - 13*j == -12*e;
  loop invariant v >= e;
  loop invariant v == 13*j - 12*e;
  loop invariant v - e == 13*(j - e);
  loop assigns v, j;
*/
while (1) {
      if (j>=e) {
          break;
      }
      v = v+1;
      j = j+1;
      v = v+g+g;
  }

}
