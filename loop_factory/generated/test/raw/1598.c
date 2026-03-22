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
