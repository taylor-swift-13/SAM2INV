int main1(int k,int n){
  int b, g, e, l;

  b=(n%8)+16;
  g=0;
  e=k;
  l=k;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (g<=b-1) {
      l = l+l;
      l = l+e;
      g = g+1;
  }
/*@
  assert !(g<=b-1) &&
         (0 <= g);
*/

}
