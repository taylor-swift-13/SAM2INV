int main1(){
  int oxd, ij, mh, i3u, ba;

  oxd=(1%36)+6;
  ij=oxd;
  mh=oxd;
  i3u=0;
  ba=-4;

  while (1) {
      if (!(ij!=mh)) {
          break;
      }
      if (ij>mh) {
          ij = ij - mh;
          ba = ba + i3u;
      }
      else {
          mh = mh - ij;
          i3u = i3u + ba;
      }
      i3u = i3u*2+4;
      ba = ba*i3u+4;
  }

}
