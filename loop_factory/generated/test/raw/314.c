int main1(){
  int sa, h, c2, s;

  sa=1+24;
  h=0;
  c2=0;
  s=0;

  while (h<sa) {
      c2 += 1;
      s++;
      if (s>=4) {
          s -= 4;
          c2 += 1;
      }
      h += 1;
  }

}
