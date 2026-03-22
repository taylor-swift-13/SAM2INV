int main1(){
  int wy15, owt, os, f2;
  wy15=0;
  owt=0;
  os=0;
  f2=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f2 + owt == 6;
  loop invariant os == owt;
  loop invariant f2 >= 0;
  loop invariant wy15 >= 0;
  loop invariant wy15 % 2 == 0;
  loop assigns wy15, f2, owt, os;
*/
while (f2>0) {
      wy15 = wy15+1*1;
      f2 = f2 - 1;
      owt = owt+1*1;
      os = os+1*1;
      wy15 = wy15*2;
  }
}