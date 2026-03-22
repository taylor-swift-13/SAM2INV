int main1(int a,int h){
  int vsw, cp, v, jdk8, qj, i, dbv, iia;
  vsw=a;
  cp=0;
  v=17;
  jdk8=0;
  qj=1;
  i=0;
  dbv=-1;
  iia=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vsw == \at(a, Pre);
  loop invariant qj == cp + 1;
  loop invariant h == \at(h, Pre) + cp*vsw - cp*(cp+1)/2;
  loop invariant a == \at(a, Pre) + (cp/6);
  loop invariant dbv == cp - 1;
  loop invariant v + jdk8 == 17;
  loop invariant 0 <= cp;
  loop invariant 0 <= v;
  loop invariant jdk8 >= 0;
  loop invariant iia == 0 + cp*(vsw - 1) - (cp*(cp+1))/2;
  loop assigns a, cp, dbv, h, i, iia, jdk8, qj, v;
*/
while (1) {
      if (!(v>0&&cp<vsw)) {
          break;
      }
      if (v<=qj) {
          i = v;
      }
      else {
          i = qj;
      }
      v = v - i;
      qj = qj + 1;
      jdk8 = jdk8 + i;
      cp++;
      if ((cp%6)==0) {
          a++;
      }
      h = h+vsw-cp;
      iia = iia+vsw-cp;
      dbv++;
      iia -= 1;
  }
}