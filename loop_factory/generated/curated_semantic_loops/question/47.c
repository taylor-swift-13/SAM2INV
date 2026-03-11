int main1(int q){
  int r, o, e, v;

  r=47;
  o=r;
  e=o;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (o-2>=0) {
      o = o-2;
  }
/*@
  assert !(o-2>=0) &&
         (r == 47);
*/

}
