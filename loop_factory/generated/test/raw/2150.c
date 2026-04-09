int main1(int v){
  int i, of2n, lgnc, vk;

  i=v;
  of2n=0;
  lgnc=0;
  vk=0;

  while (of2n < i) {
      of2n++;
      vk = 1 - vk;
      lgnc = 1 - lgnc;
      v += lgnc;
  }

}
