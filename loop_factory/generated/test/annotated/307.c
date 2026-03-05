int main1(int u,int s){
  int r, etp7, fks;
  r=42;
  etp7=0;
  fks=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fks == etp7 % 2;
  loop invariant 0 <= etp7;
  loop invariant etp7 <= r;
  loop invariant s == \at(s, Pre);
  loop invariant u == \at(u, Pre) + ((etp7 + 1) / 2);
  loop invariant 0 <= fks;
  loop invariant fks <= 1;
  loop assigns etp7, fks, u;
*/
while (etp7<r) {
      if (fks==0) {
          fks = fks + 3;
          fks = fks - 3;
          fks = 1;
      }
      else {
          fks = fks - 3;
          fks = fks + 3;
          fks = 0;
      }
      etp7 = etp7 + 1;
      u += fks;
  }
}