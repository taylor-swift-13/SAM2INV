int main1(int s){
  int r, k, eam;
  r=(s%27)+5;
  k=r;
  eam=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == ((\at(s, Pre) % 27) + 5);
  loop invariant k == r;
  loop invariant s - \at(s,Pre) == (eam - \at(s,Pre)) * r;
  loop invariant eam >= \at(s,Pre);
  loop assigns eam, s;
*/
while (k>=1) {
      if (k<r/2) {
          eam = eam + eam;
      }
      else {
          eam++;
      }
      s += r;
  }
}