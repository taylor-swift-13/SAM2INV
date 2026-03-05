int main1(int n,int d){
  int pkgw, ty6c, q, wk;

  pkgw=56;
  ty6c=pkgw;
  q=0;
  wk=0;

  while (ty6c<pkgw) {
      q += 1;
      wk++;
      if (wk>=4) {
          wk -= 4;
          q += 1;
      }
      ty6c = ty6c + 1;
  }

}
