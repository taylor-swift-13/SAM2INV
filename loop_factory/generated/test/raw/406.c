int main1(int v){
  int yt, pz, ce, fr;

  yt=v+6;
  pz=0;
  ce=0;
  fr=1;

  while (pz<yt) {
      if (ce>=10) {
          fr = -1;
      }
      if (ce<=0) {
          fr = 1;
      }
      ce += fr;
      pz = pz + 1;
  }

}
