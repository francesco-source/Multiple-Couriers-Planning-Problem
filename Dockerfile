FROM minizinc/minizinc:latest

WORKDIR C:\Users\utente\Videos\Final Project\CDMO

COPY . .

RUN apt-get update
RUN apt-get install -y python3
RUN apt-get install -y python3-pip
RUN apt-get install -y glpk-utils
RUN python3 -m pip install -r requirements.txt
RUN apt-get install -y z3
RUN apt-get install -y cvc4

CMD python3 main.py -a lp -n 1 