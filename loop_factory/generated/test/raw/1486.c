int main1(){
  int x1, mwm, nl, xu;

  x1=1;
  mwm=-6;
  nl=8;
  xu=x1;

  while (mwm+1<=x1) {
      xu = xu + 1;
      nl = nl+xu*xu*xu*xu*xu;
      x1 = (mwm+1)-1;
  }

}
