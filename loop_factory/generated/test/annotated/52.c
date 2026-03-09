int main1(){
  int z, yw0, wyxi, c2;
  z=1-1;
  yw0=0;
  wyxi=0;
  c2=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= c2;
  loop invariant c2 <= 8;
  loop invariant z == 0;
  loop invariant wyxi == yw0*(27 - yw0)/2;
  loop invariant yw0 + c2 == 8;
  loop invariant yw0 <= z;
  loop assigns wyxi, yw0, c2;
*/
while (yw0<z&&c2>0) {
      wyxi = wyxi + c2;
      yw0 = yw0 + 1;
      wyxi = wyxi + 5;
      c2 = c2 - 1;
  }
}