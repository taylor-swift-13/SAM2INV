int main1(int i){
  int zkpo, s9, pczp, wtq;

  zkpo=i+3;
  s9=0;
  pczp=1;
  wtq=1;

  while (pczp<=zkpo) {
      s9++;
      wtq += 2;
      i = i+(s9%6);
      pczp += wtq;
  }

}
