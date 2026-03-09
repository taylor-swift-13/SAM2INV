int main1(int j,int w){
  int r, s5, bbq;

  r=-4;
  s5=(j%20)+10;
  bbq=(j%15)+8;

  for (; s5>0&&bbq>0; r = r + 1) {
      if (r%2==0) {
          s5--;
      }
      else {
          bbq--;
      }
  }

}
