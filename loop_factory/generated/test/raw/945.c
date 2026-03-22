int main1(){
  int bb, tv, lw;

  bb=0;
  tv=(1%20)+10;
  lw=(1%15)+8;

  for (; tv>0&&lw>0; bb++) {
      if (!(!(bb%2==0))) {
          tv--;
      }
      else {
          lw = lw - 1;
      }
  }

}
