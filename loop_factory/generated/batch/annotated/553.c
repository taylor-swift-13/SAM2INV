int main1(int b,int q){
  int f, j, v, i;

  f=76;
  j=0;
  v=0;
  i=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 0;
  loop invariant j >= 0;
  loop invariant j % 2 == 0;
  loop invariant f == 76;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant j <= f;
  loop assigns v, j;
*/
while (j<f) {
      v = v*v+v;
      j = j+2;
  }

}
