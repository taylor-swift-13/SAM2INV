int main1(int l){
  int ywp, gb, l5, tv;

  ywp=l+14;
  gb=0;
  l5=0;
  tv=6;

  while (gb<ywp&&tv>0) {
      gb = gb + 1;
      l5 += tv;
      tv--;
      l += tv;
  }

}
