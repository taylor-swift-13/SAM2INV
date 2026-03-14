int main1(){
  int izo, oy, wqm;

  izo=0;
  oy=(1%20)+10;
  wqm=(1%15)+8;

  while (1) {
      if (!(oy>0&&wqm>0)) {
          break;
      }
      if (!(!(izo%2==0))) {
          oy -= 1;
      }
      else {
          wqm = wqm - 1;
      }
      izo += 1;
  }

}
