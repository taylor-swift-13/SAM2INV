int main1(int r,int x){
  int vae, zz, s;
  vae=x*2;
  zz=0;
  s=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vae == x*2;
  loop invariant 0 <= zz;
  loop invariant s == 7 + zz * (r + x + 1);
  loop assigns s, zz;
*/
while (1) {
      if (!(zz+1<=vae)) {
          break;
      }
      s = s+r+x;
      s++;
      zz++;
  }
}