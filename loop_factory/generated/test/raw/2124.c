int main1(int r){
  int u8wl, pay, qk, vnq, t3p3;

  u8wl=r;
  pay=0;
  qk=0;
  vnq=0;
  t3p3=u8wl;

  while (1) {
      if (!(pay < u8wl)) {
          break;
      }
      pay = pay + 1;
      t3p3 += pay;
      qk = qk + 1 - (pay % 2);
      vnq = vnq + (pay % 2);
  }

}
