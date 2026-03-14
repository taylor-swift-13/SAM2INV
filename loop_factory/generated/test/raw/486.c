int main1(){
  int zydq, ji, rw, o7, kin7;

  zydq=(1%27)+19;
  ji=0;
  rw=0;
  o7=0;
  kin7=(1%18)+5;

  while (kin7>0) {
      kin7 = kin7 - 1;
      rw = rw+1*1;
      ji = ji+1*1;
      o7 = o7+1*1;
      ji = ji*2;
  }

  while (rw>kin7) {
      rw = rw - kin7;
      kin7 += 1;
      zydq = zydq + rw;
      zydq = zydq*3+1;
  }

}
