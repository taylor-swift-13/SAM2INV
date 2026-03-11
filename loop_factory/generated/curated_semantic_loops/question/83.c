int main1(int k,int q){
  int h, j, t;

  h=64;
  j=0;
  t=h;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (j<=h-1) {
      t = t*2;
      t = t%8;
      j = j+1;
  }
/*@
  assert !(j<=h-1) &&
         (h == 64 && j <= h && (t == 0 || t == 64) && t % 8 == 0);
*/

}
