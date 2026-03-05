int main1(){
  int zn, v5j, ocj;
  zn=(1%38)+4;
  v5j=0;
  ocj=v5j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= v5j;
  loop invariant v5j <= zn;
  loop invariant 0 <= ocj && ocj <= zn + 1 && (ocj == 4*v5j || ocj == zn + 1);
  loop invariant ocj <= 4*v5j;
  loop assigns ocj, v5j;
*/
while (1) {
      if (ocj+3<=zn) {
          ocj = ocj + 3;
      }
      else {
          ocj = zn;
      }
      ocj++;
      v5j++;
      if (v5j>=zn) {
          break;
      }
  }
}