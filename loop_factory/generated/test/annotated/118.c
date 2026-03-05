int main1(int v,int p){
  int tsh, m7, pu;
  tsh=76;
  m7=0;
  pu=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= pu <= tsh;
  loop invariant p == \at(p, Pre);
  loop invariant v == \at(v, Pre);
  loop invariant m7 >= 0;
  loop invariant m7 >= pu;
  loop invariant tsh == 76;
  loop invariant (pu == 0) || (1 <= pu && pu <= tsh);
  loop assigns pu, m7;
*/
while (pu>0&&pu<=tsh) {
      if (pu>pu) {
          pu = pu - pu;
      }
      else {
          pu = 0;
      }
      pu++;
      m7 += 1;
  }
}