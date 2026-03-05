int main1(int j){
  int gi5, opo, ue, lt3;

  gi5=23;
  opo=0;
  ue=0;
  lt3=1;

  for (; ue>0&&lt3<=gi5; opo++) {
      if (ue>lt3) {
          ue = ue - lt3;
      }
      else {
          ue = 0;
      }
      ue += 1;
      lt3 += 1;
  }

}
