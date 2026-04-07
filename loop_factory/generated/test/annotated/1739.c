int main1(int t){
  int kra, l, z, lu;
  kra=t+18;
  l=0;
  z=0;
  lu=kra;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == z % 5;
  loop invariant lu == kra + (z/5)*10 + ((z%5) * ((z%5) + 1)) / 2;
  loop invariant 0 <= z;
  loop assigns z, l, lu;
*/
while (1) {
      if (!(z<kra)) {
          break;
      }
      z += 1;
      l = (l+1)%5;
      lu += l;
  }
}