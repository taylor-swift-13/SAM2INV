int main1(int y){
  int q, nf, e5;

  q=0;
  nf=(y%20)+10;
  e5=(y%15)+8;

  for (; nf>0&&e5>0; q += 1) {
      if (q%2==0) {
          nf = nf - 1;
      }
      else {
          e5 -= 1;
      }
  }

}
