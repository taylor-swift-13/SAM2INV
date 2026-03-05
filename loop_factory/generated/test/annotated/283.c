int main1(int j,int p){
  int yv, o74, vfe;
  yv=(p%40)+15;
  o74=yv;
  vfe=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vfe == 0 || vfe == 1;
  loop invariant j == \at(j, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant o74 - vfe >= yv;
  loop invariant yv == (p % 40) + 15;
  loop assigns o74, vfe;
*/
while (vfe>0&&vfe<=yv) {
      if (vfe>vfe) {
          vfe = vfe - vfe;
      }
      else {
          vfe = 0;
      }
      vfe = vfe + 1;
      o74 += 1;
  }
}