int main1(int k,int q){
  int h, j, t;

  h=64;
  j=h;
  t=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= j && j <= 64;
  loop invariant h == 64;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t <= -5;
  loop invariant t % 5 == 0;
  loop invariant j >= 0;
  loop assigns t, j;
*/
while (j>0) {
      if ((j%4)==0) {
          t = t+t;
      }
      j = j-1;
  }

}
