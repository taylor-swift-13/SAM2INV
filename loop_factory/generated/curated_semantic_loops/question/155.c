int main1(int m,int q){
  int i, e, o;

  i=(q%17)+16;
  e=0;
  o=m;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (e<i) {
      o = o+(-8);
      e = e+1;
  }
/*@
  assert !(e<i) &&
         (o == \at(m, Pre) - 8*e);
*/

}
