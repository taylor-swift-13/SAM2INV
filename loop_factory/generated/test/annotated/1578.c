int main1(int i){
  int uq, ax, e4, ow, sp9, s9, vk, g5, zh8j, myp;
  uq=i;
  ax=0;
  e4=3;
  ow=4;
  sp9=0;
  s9=0;
  vk=-4;
  g5=uq;
  zh8j=i;
  myp=uq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sp9 == ax;
  loop invariant ow == 4;
  loop invariant e4 == 3 + ax;
  loop invariant s9 == ax*(ax + 1)/2 + 5*ax;
  loop invariant uq == i;
  loop invariant ax >= 0 && (uq >= 0 ==> ax <= uq);
  loop invariant zh8j == uq;
  loop invariant myp == uq + ax;
  loop invariant g5 == uq + (ax * (ax + 1)) / 2;
  loop invariant 0 <= ax;
  loop invariant uq == \at(i,Pre);
  loop assigns sp9, ow, e4, ax, zh8j, myp, g5, s9, vk;
*/
while (1) {
      if (!(ax<=uq-1)) {
          break;
      }
      sp9 += 1;
      ow += 1;
      if (ow>=1) {
          ow = ow - 1;
          e4 = e4 + 1;
      }
      ax++;
      if (zh8j+3<uq) {
          zh8j = zh8j + ax;
      }
      myp = myp + 1;
      g5 = g5 + ax;
      s9 = s9 + ax;
      s9 = s9 + 5;
      vk += s9;
  }
}