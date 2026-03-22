int main1(){
  int zh, ur, ek, q3, xm, a5x;

  zh=(1%31)+6;
  ur=zh;
  ek=zh;
  q3=-6;
  xm=(1%6)+2;
  a5x=-5;

  while (1) {
      if (q3>=zh) {
          break;
      }
      q3 += 1;
      a5x += zh;
      ur = ur*xm+1;
      ek = ek*xm;
  }

}
