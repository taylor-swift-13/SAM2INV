int main1(int g){
  int b89, rzv, de, i96, zs, nr7;

  b89=g+3;
  rzv=3;
  de=0;
  i96=g;
  zs=0;
  nr7=0;

  while (rzv<=b89) {
      de = de+rzv*rzv;
      nr7 = nr7+(de%2);
      g += 2;
      rzv = rzv + 1;
      zs = zs + 1;
      nr7 = nr7*nr7+i96;
      i96 = i96%4;
  }

}
