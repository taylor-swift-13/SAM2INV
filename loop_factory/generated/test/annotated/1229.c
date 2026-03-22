int main1(int g,int q){
  int wp, momq, rx, n4vk, yb, mt, e;
  wp=g;
  momq=1;
  rx=4;
  n4vk=momq;
  yb=0;
  mt=3;
  e=wp;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mt >= 3;
  loop invariant yb == 6*(mt - 3);
  loop invariant n4vk == 1 + 3*(mt - 3)*(mt - 4);
  loop invariant rx == 4 + (mt - 3) + (mt - 3)*(mt - 4)*(mt - 5);
  loop invariant e == wp + 3*(mt - 3)*(mt - 2);
  loop invariant e   == g + 3*(mt - 3)*(mt - 2);
  loop invariant rx == 4 + (mt - 3) + (mt - 4)*(mt - 3)*(mt - 5);
  loop assigns rx, n4vk, yb, mt, e;
*/
while (1) {
      if (mt>wp) {
          break;
      }
      rx = rx + n4vk;
      n4vk = n4vk + yb;
      yb += 6;
      mt = mt + 1;
      e = e + yb;
  }
}