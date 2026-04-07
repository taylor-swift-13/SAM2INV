int main1(){
  int l, r, iz, rp;

  l=(1%25)+8;
  r=1;
  iz=r;
  rp=20;

  while (iz<=l-1) {
      rp += r;
      iz += 8;
      rp++;
  }

}
