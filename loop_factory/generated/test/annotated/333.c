int main1(int y,int t){
  int qp, gw2, p1, ha;
  qp=40;
  gw2=0;
  p1=0;
  ha=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gw2 == ha - 1;
  loop invariant 0 <= p1;
  loop invariant p1 <= qp;
  loop invariant 1 <= ha;
  loop invariant ha <= qp + 1;
  loop invariant t == \at(t, Pre);
  loop invariant y == \at(y, Pre);
  loop invariant qp == 40;
  loop invariant p1 <= ha;
  loop assigns p1, ha, gw2;
*/
while (p1>0&&ha<=qp) {
      if (p1>ha) {
          p1 = p1 - ha;
      }
      else {
          p1 = 0;
      }
      p1 += 1;
      ha = ha + 1;
      gw2 += 1;
  }
}