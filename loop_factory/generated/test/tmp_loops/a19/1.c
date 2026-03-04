int main1(int l,int g){
  int bz, o;

  bz=l+8;
  o=(l%15)+3;

  while (o!=0) {
      o--;
      l += bz;
  }

}
