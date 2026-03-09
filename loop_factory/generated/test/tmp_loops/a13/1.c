int main1(int u){
  int sha, bo, dd;

  sha=u*3;
  bo=-1;
  dd=u;

  while (bo<sha) {
      dd = sha-bo;
      u += dd;
      bo = bo + 3;
  }

}
