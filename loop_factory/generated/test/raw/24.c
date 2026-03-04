int main1(int k,int g){
  int phg, r5c, qi;

  phg=0;
  r5c=(g%20)+5;
  qi=3;

  while (1) {
      if (!(r5c>0)) {
          break;
      }
      r5c = r5c - 1;
      qi = qi + phg;
      k += 2;
      g += r5c;
  }

}
