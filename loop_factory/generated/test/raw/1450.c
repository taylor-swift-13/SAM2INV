int main1(){
  int nun5, whsx, rl;

  nun5=1+22;
  whsx=0;
  rl=nun5;

  while (1) {
      if (!(whsx<nun5)) {
          break;
      }
      if (whsx>=nun5/2) {
          rl += 4;
      }
      rl += rl;
      whsx += 1;
  }

}
