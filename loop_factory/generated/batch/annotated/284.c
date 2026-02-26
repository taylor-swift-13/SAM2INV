int main1(int k,int q){
  int h, j, t;

  h=64;
  j=0;
  t=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 64;
  loop invariant j <= h - 1;
  loop invariant t >= 64;
  loop invariant t % 2 == 0;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t % 4 == 0;
  loop invariant 0 <= j;
  loop invariant j <= h;
  loop invariant t % 68 == 64;
  loop invariant t >= h;
  loop invariant t >= 0;
  loop invariant j == 0;
  loop assigns t;
*/
while (j<=h-1) {
      t = t+2;
      t = t+t;
  }

}
