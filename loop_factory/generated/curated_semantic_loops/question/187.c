int main1(int k,int q){
  int i, u, o, r;

  i=59;
  u=i;
  o=0;
  r=0;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (o<i) {
      if (o<i/2) {
          r = r+3;
      }
      else {
          r = r-3;
      }
      o = o+1;
      o = o+3;
  }
/*@
  assert !(o<i) &&
         (o % 4 == 0);
*/

}
