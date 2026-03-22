int main1(int i){
  int q, kp, x;

  q=1;
  kp=(i%20)+10;
  x=(i%15)+8;

  while (1) {
      if (!(kp>0&&x>0)) {
          break;
      }
      if (q%2==0) {
          kp--;
      }
      else {
          x--;
      }
      q += 1;
  }

}
