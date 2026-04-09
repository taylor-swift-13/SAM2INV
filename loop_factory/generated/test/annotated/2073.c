int main1(int x){
  int jh0, itu, ue, zygf;
  jh0=x*5;
  itu=0;
  ue=2;
  zygf=itu;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jh0 == x * 5;
  loop invariant (itu == 0 ==> ue == 2) && (itu > 0 ==> ue == jh0 - itu);
  loop invariant (itu == 0 ==> zygf == 0) && (itu > 0 ==> zygf == x - itu);
  loop invariant itu >= 0;
  loop invariant ((itu == 0 && ue == 2 && zygf == 0) ||
                    (1 <= itu && itu <= jh0 && ue == jh0 - itu && zygf == x - itu));
  loop invariant (itu == 0 || itu <= jh0);
  loop invariant jh0 == 5 * \at(x, Pre);
  loop invariant (itu == 0 && ue == 2 && zygf == 0)
                   || (itu > 0 && (ue + itu) == jh0 && zygf == (\at(x, Pre) - itu));
  loop assigns itu, zygf, ue;
*/
while (1) {
      if (!(itu < jh0)) {
          break;
      }
      itu += 1;
      zygf = (x)+(-(itu));
      ue = jh0-itu;
  }
}