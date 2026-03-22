int main1(int p){
  int ky, agn4, tw, lq;

  ky=p;
  agn4=2;
  tw=0;
  lq=agn4;

  while (tw<ky) {
      if (!(!(tw>=ky/2))) {
          lq += 4;
      }
      tw++;
      p = p+tw-tw;
  }

}
