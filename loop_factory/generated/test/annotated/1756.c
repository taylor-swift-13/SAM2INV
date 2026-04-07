int main1(int p){
  int viq, ht, yw, go9, zm6a;
  viq=p+6;
  ht=0;
  yw=6;
  go9=ht;
  zm6a=viq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ht;
  loop invariant zm6a == viq + 2*ht;
  loop invariant yw >= 6;
  loop invariant go9 == 2*yw - 12;
  loop invariant viq == \at(p, Pre) + 6;
  loop assigns yw, ht, zm6a, go9;
*/
while (ht < viq) {
      yw = yw*2;
      ht++;
      zm6a += 2;
      go9 += yw;
  }
}