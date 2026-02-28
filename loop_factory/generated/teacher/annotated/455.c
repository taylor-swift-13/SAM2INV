int main1(int k,int q){
  int h, j, t;

  h=64;
  j=0;
  t=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 64;
  loop invariant j == 0;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t >= 64;
  loop invariant t % 3 == 1;
  loop invariant (j % 8) == 0;
  loop invariant (t - 64) % 3 == 0;
  loop assigns t;
*/
while (1) {
      t = t+2;
      if ((j%8)==0) {
          t = t+j;
      }
      t = t+1;
  }

}
