int main1(){
  int rlb, rzm, po, zk, ayy;

  rlb=76;
  rzm=rlb;
  po=-2;
  zk=rzm;
  ayy=rlb;

  while (rzm>0) {
      zk++;
      ayy = ayy + zk;
      po = po+zk*zk*zk*zk*zk;
      rzm = 0;
  }

}
