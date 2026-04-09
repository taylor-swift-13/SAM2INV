int main1(){
  int g, zk, shq, niss, rv28;

  g=1+11;
  zk=0;
  shq=5;
  niss=zk;
  rv28=-6;

  while (zk < g) {
      niss = zk % 2 == 0 ? niss + shq : niss + rv28;
      zk++;
      shq = shq + zk;
  }

}
