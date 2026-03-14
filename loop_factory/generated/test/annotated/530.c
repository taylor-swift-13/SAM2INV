int main1(int i,int q){
  int j1, wy, e, f7, zuo8, j, uk3;
  j1=(q%11)+15;
  wy=j1;
  e=0;
  f7=0;
  zuo8=0;
  j=0;
  uk3=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i, Pre) + e * wy;
  loop invariant 0 <= e <= j1;
  loop invariant j + zuo8 + f7 + uk3 == e;
  loop invariant wy == j1;
  loop assigns i, e, j, zuo8, f7, uk3;
*/
while (e<=j1-1) {
      if (!(!(e%11==0))) {
          if (e%9==0) {
              j++;
          }
          else {
              if (e%5==0) {
                  zuo8++;
              }
              else {
                  f7++;
              }
          }
      }
      else {
          uk3 += 1;
      }
      i += wy;
      e += 1;
  }
}