int main1(int m,int j){
  int x5d, gw0;
  x5d=j;
  gw0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x5d == j;
  loop invariant 0 <= gw0;
  loop invariant (j >= 0) ==> (gw0 <= j);
  loop assigns gw0;
*/
while (1) {
      if (!(gw0<=x5d-1)) {
          break;
      }
      gw0 = gw0 + 1;
  }
}