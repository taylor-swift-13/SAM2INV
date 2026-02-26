int main1(int n,int q){
  int w, f, v;

  w=q-7;
  f=0;
  v=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 1;
  loop invariant f >= 0;
  loop invariant q == \at(q, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant w == q - 7;
  loop invariant 0 <= f;

  loop invariant f <= w || w < 0;
  loop assigns f, v;
*/
while (f+1<=w) {
      v = v%5;
      f = f+1;
  }

}
